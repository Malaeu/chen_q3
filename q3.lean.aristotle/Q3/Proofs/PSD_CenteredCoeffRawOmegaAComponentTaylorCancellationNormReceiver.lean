import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAHRawLanding

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Direct-norm receiver adapters for the Step33A.1-A cancellation RHS.

The P45 bridge rewrites

  deriv residual - residualTaylorCoeff polynomial

as the scaled cancellation RHS.  This file wires that exact object into the
existing full-Taylor direct-norm receiver.  It does not prove the numeric RHS
bound; callers must still provide proof-grade bounds for the full scaled RHS
and for the residual Taylor polynomial.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff : Real :=
  (((3 : Real) / 10) / Real.pi)

def primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        eta +
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs
    (eta : Real) :
    deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta =
      primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta := by
  rw [primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm]
  simpa [primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs,
    primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff] using
    primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_cancellationRhs
      eta

theorem primaryFiniteRow0Parent0Split100Sub0_scaledCancellationRhs_norm_bound_of_component_bounds
    {activeScaleAbs scaleMismatchAbs cancellationBound nominalBound
      interpolationError : Real}
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        activeScaleAbs)
    (hScaleMismatchAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| <=
        scaleMismatchAbs)
    (hCancellationBound :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        |primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
          eta| <= cancellationBound)
    (hNominalBound :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        |primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta| <=
          nominalBound)
    (hBudget :
      activeScaleAbs * cancellationBound +
          scaleMismatchAbs * nominalBound <= interpolationError) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta‖ <=
        interpolationError := by
  intro eta hEta
  have hActiveScaleAbsNonneg : 0 <= activeScaleAbs :=
    (abs_nonneg primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff).trans
      hActiveScaleAbs
  have hScaleMismatchAbsNonneg : 0 <= scaleMismatchAbs :=
    (abs_nonneg
      (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real))).trans
      hScaleMismatchAbs
  have hTermCancellation :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta| <=
        activeScaleAbs * cancellationBound := by
    calc
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta|
          =
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
          |primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta| := by
          rw [abs_mul]
      _ <= activeScaleAbs * cancellationBound :=
        mul_le_mul hActiveScaleAbs (hCancellationBound eta hEta)
          (abs_nonneg _)
          hActiveScaleAbsNonneg
  have hTermNominal :
      |(primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta| <=
        scaleMismatchAbs * nominalBound := by
    calc
      |(primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta|
          =
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| *
          |primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta| := by
          rw [abs_mul]
      _ <= scaleMismatchAbs * nominalBound :=
        mul_le_mul hScaleMismatchAbs (hNominalBound eta hEta)
          (abs_nonneg _)
          hScaleMismatchAbsNonneg
  calc
    ‖primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta‖ =
        |primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta| := by
        rw [Real.norm_eq_abs]
    _ <=
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta| +
          |(primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta| := by
        dsimp [primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs]
        exact abs_add_le _ _
    _ <=
        activeScaleAbs * cancellationBound +
          scaleMismatchAbs * nominalBound :=
        add_le_add hTermCancellation hTermNominal
    _ <= interpolationError := hBudget

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_bound_of_scaledCancellationRhs_bound
    {interpolationError : Real}
    (hScaledRhsBoundOnCell :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta‖ <=
          interpolationError) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta‖ <=
        interpolationError := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs]
  exact hScaledRhsBoundOnCell eta hEta

def primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_interpolation_error_bound
    (modelDeriv : Real → Real)
    {modelBound interpolationError : Real}
    (hModel :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖modelDeriv eta‖ <= modelBound)
    (hError :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta -
          modelDeriv eta‖ <= interpolationError)
    (hBudget :
      interpolationError + modelBound <=
        ((1866608532757 : Real) /
          500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert :=
  primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_norm_bound
    (by
      intro eta hEta
      calc
        ‖deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta‖ =
            ‖(deriv
                  primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
                  eta -
                modelDeriv eta) + modelDeriv eta‖ := by
              rw [sub_add_cancel]
        _ <=
            ‖deriv
                primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
                eta -
              modelDeriv eta‖ + ‖modelDeriv eta‖ :=
            norm_add_le _ _
        _ <= interpolationError + modelBound :=
            add_le_add (hError eta hEta) (hModel eta hEta)
        _ <=
            ((1866608532757 : Real) /
              500000000000000000000000000000) :=
            hBudget)

def primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_bound
    {modelBound interpolationError : Real}
    (hResidualTaylorModel :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta‖ <=
          modelBound)
    (hScaledRhsBoundOnCell :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta‖ <=
          interpolationError)
    (hBudget :
      interpolationError + modelBound <=
        ((1866608532757 : Real) /
          500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert :=
  primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_interpolation_error_bound
    (rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff)
    hResidualTaylorModel
    (primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_bound_of_scaledCancellationRhs_bound
      hScaledRhsBoundOnCell)
    hBudget

def primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_polynomial_model_bound
    {modelRadius modelBound interpolationError : Real}
    (hModelRadius :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        |eta - (((1 : Rat) / 20 : Rat) : Real)| <= modelRadius)
    (hResidualTaylorModelSum :
      (∑ i : Fin
          (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1),
        |(primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff i :
            Real)| * modelRadius ^ i.1) <= modelBound)
    (hScaledRhsBoundOnCell :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta‖ <=
          interpolationError)
    (hBudget :
      interpolationError + modelBound <=
        ((1866608532757 : Real) /
          500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert :=
  primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_bound
    (by
      intro eta hEta
      have hPoly :
          |rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta| <=
            modelBound :=
        le_trans
          (abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
            (hModelRadius eta hEta))
          hResidualTaylorModelSum
      simpa [Real.norm_eq_abs] using hPoly)
    hScaledRhsBoundOnCell
    hBudget

end Step33
end PSDpd
end Q3
