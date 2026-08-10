import Q3.Proofs.RouteB.D0PstarW02EndpointFunctionals
import Q3.Proofs.RouteB.D0PstarW02RankTwoForm

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- Literal positive source-W02 endpoint value on a logarithmic mode. -/
noncomputable def sourceW02EndpointPlusModeValue
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (x / 2) : ℂ)

/-- Literal negative source-W02 endpoint value on a logarithmic mode. -/
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

theorem sourceW02ModePairing_eq_rankTwoEndpointModeValues
    (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      star (sourceW02EndpointMinusModeValue i n) *
          sourceW02EndpointPlusModeValue i r +
        star (sourceW02EndpointPlusModeValue i n) *
          sourceW02EndpointMinusModeValue i r := by
  simpa [sourceW02EndpointPlusModeValue,
    sourceW02EndpointMinusModeValue] using
    sourceW02ModePairing_eq_rankTwoEndpointIntegrals i n r

/-- Bounded ambient W02 form assembled from the two explicit physical
endpoint functionals. Its construction does not use the finite CCM matrix. -/
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
    (i : PairIndex) (n r : ℤ) :
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
    (sourceW02ModePairing_eq_rankTwoEndpointModeValues i) n r

theorem sourceW02AmbientContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmW02
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceW02AmbientContinuousSesquilinearForm i
        (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmW02Entry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k := by
  exact
    endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmW02
      i
      (sourceW02PhysicalEndpointPlusFunctional i)
      (sourceW02PhysicalEndpointMinusFunctional i)
      (sourceW02EndpointPlusModeValue i)
      (sourceW02EndpointMinusModeValue i)
      (sourceW02PhysicalEndpointPlusFunctional_apply_modeValue i)
      (sourceW02PhysicalEndpointMinusFunctional_apply_modeValue i)
      (sourceW02ModePairing_eq_rankTwoEndpointModeValues i) c d

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

#print axioms sourceW02ModePairing_eq_rankTwoEndpointModeValues
#print axioms sourceW02AmbientContinuousSesquilinearForm
#print axioms sourceW02AmbientContinuousSesquilinearForm_conj_symm
#print axioms sourceW02AmbientContinuousSesquilinearForm_apply_mode
#print axioms sourceW02AmbientContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmW02

end Q3.RouteB.D0Pstar
