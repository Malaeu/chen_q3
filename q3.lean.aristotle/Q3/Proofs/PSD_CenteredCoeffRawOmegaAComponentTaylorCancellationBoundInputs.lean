import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Bound-input adapter for the Step33A.1-A sub0 cancellation route.

This file does not close the numeric Step33A.1-A budget.  It proves the easy
same-normalization inputs for the scaled cancellation RHS receiver, and it
records two exact constant-fail certificates for the attempted triangle split:
the coefficient-sum P45 model bound is too large, and even the actual P45
residualTaylor polynomial at the center already exceeds the final slope.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalAbsBound :
    Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget

def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBoundRat : Rat :=
  ∑ i : Fin
      (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1),
    |primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff i| *
      ((1 : Rat) / 20) ^ i.1

def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound : Real :=
  (primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBoundRat : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylorModelBound_final_slope_fail_rat :
    ((1866608532757 : Rat) /
        500000000000000000000000000000) <
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBoundRat := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylorModelBound_final_slope_fail :
    ((1866608532757 : Real) /
        500000000000000000000000000000) <
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound := by
  have hRat :=
    primaryFiniteRow0Parent0Split100Sub0_residualTaylorModelBound_final_slope_fail_rat
  have hReal :
      (((1866608532757 : Rat) /
          500000000000000000000000000000 : Rat) : Real) <
        (primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBoundRat :
          Real) := by
    exact_mod_cast hRat
  simpa [primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound] using
    hReal

def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCenterAbsRat : Rat :=
  |primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff 0|

theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylor_center_abs_final_slope_fail_rat :
    ((1866608532757 : Rat) /
        500000000000000000000000000000) <
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCenterAbsRat := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylor_polynomial_center_abs_final_slope_fail :
    ((1866608532757 : Real) /
        500000000000000000000000000000) <
      |rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
        (((1 : Rat) / 20 : Rat) : Real)| := by
  have hRat :=
    primaryFiniteRow0Parent0Split100Sub0_residualTaylor_center_abs_final_slope_fail_rat
  have hReal :
      (((1866608532757 : Rat) /
          500000000000000000000000000000 : Rat) : Real) <
        (primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCenterAbsRat :
          Real) := by
    exact_mod_cast hRat
  rw [
    rawOmegaATaylorPolynomial_center
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff]
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCenterAbsRat,
    Rat.cast_abs] using hReal

theorem primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    |eta - (((1 : Rat) / 20 : Rat) : Real)| <= (1 : Real) / 20 := by
  rw [abs_le]
  constructor
  · have hLeft := hEta.1
    norm_num at hLeft ⊢
    linarith
  · have hRight := hEta.2
    norm_num at hRight ⊢
    linarith

theorem primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound :
    |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) := by
  have hInterval :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_mem_tightInterval
  rw [abs_of_nonneg]
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound] using
      hInterval.2
  · have hTightLowerNonneg :
        0 <= (primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Real) := by
      norm_num [primaryFiniteRow0Parent0Split100Sub0TightScaleLower]
    exact hTightLowerNonneg.trans
      (by
        simpa [primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff] using
          hInterval.1)

theorem primaryFiniteRow0Parent0Split100Sub0_activeScale_nominalScale_abs_error :
    |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| <=
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) := by
  have hInterval :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_mem_tightInterval
  simpa [primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff] using
    primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_error_of_active_interval
      hInterval.1 hInterval.2

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_abs_bound :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      |primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta| <=
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalAbsBound := by
  intro eta hEta
  have hRadius :=
    primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  have hOmegaPrime :=
    primaryFiniteRow0Parent0Split100Sub0_omegaPrime_nominal_abs_budget hRadius
  have hShapeSq :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSq_nominal_abs_budget hRadius
  have hOmega :=
    primaryFiniteRow0Parent0Split100Sub0_omega_nominal_abs_budget hRadius
  have hShapeSqDeriv :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_nominal_abs_budget
      hRadius
  have hFirst :
      |primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta| <=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget := by
    exact
      primaryFiniteRow0Parent0Split100Sub0_product_summand_abs_bridge
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly] using
            hOmegaPrime)
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly] using
            hShapeSq)
        le_rfl
  have hSecond :
      |primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta| <=
        primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget := by
    exact
      primaryFiniteRow0Parent0Split100Sub0_product_summand_abs_bridge
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly] using
            hOmega)
        (by
          simpa [
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly] using
            hShapeSqDeriv)
        le_rfl
  calc
    |primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta| <=
        |primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta| +
          |primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta| := by
        dsimp [primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal]
        exact abs_add_le _ _
    _ <= primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalAbsBound := by
        dsimp [
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalAbsBound]
        exact add_le_add hFirst hSecond

theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylor_model_bound :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound := by
  intro eta hEta
  have hRadius :=
    primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  have hPoly :
      |rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta| <=
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound :=
    (abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
      hRadius).trans
      (by
        dsimp [
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound,
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBoundRat]
        simp [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_abs])
  simpa [Real.norm_eq_abs] using hPoly

def primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_cancellationResidual_bound
    {cancellationBound scaledRhsInterpolationError : Real}
    (hCancellationBound :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        |primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
          eta| <= cancellationBound)
    (hScaledBudget :
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          cancellationBound +
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalAbsBound <=
        scaledRhsInterpolationError)
    (hFinalBudget :
      scaledRhsInterpolationError +
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound <=
        ((1866608532757 : Real) /
          500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert :=
  primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_polynomial_model_bound
    (modelRadius := (1 : Real) / 20)
    (modelBound :=
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound)
    (interpolationError := scaledRhsInterpolationError)
    (by
      intro eta hEta
      exact
        primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta)
    (by
      dsimp [
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBound,
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorModelBoundRat]
      simp [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_abs])
    (primaryFiniteRow0Parent0Split100Sub0_scaledCancellationRhs_norm_bound_of_component_bounds
      primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound
      primaryFiniteRow0Parent0Split100Sub0_activeScale_nominalScale_abs_error
      hCancellationBound
      primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_abs_bound
      hScaledBudget)
    hFinalBudget

end Step33
end PSDpd
end Q3
