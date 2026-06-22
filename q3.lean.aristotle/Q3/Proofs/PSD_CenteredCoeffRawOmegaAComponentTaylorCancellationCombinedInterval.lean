import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Combined interval receiver for the Step33A.1-A sub0 cancellation route.

The separate triangle split

  deriv residual = residualTaylor polynomial + ScaledCancellationRhs

cannot close because the residualTaylor polynomial is already too large at the
center.  This file exposes the next live proof surface: a proof-grade interval
certificate for the combined expression before taking any absolute value.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta +
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_combinedCancellationIntervalExpr
    (eta : Real) :
    deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta := by
  have h :=
    primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs
      eta
  dsimp [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr]
  linarith

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds
    (hCombined :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ((-94119513411 : Real) /
            500000000000000000000000000000) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <=
          ((1866608532757 : Real) /
            500000000000000000000000000000)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ((-94119513411 : Real) /
          500000000000000000000000000000) <=
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
          eta ∧
      deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
          eta <=
        ((1866608532757 : Real) /
          500000000000000000000000000000) := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_combinedCancellationIntervalExpr]
  exact hCombined eta hEta

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_closedForm_residual_bounds_of_combined_bounds
    (hCombined :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ((-94119513411 : Real) /
            500000000000000000000000000000) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <=
          ((1866608532757 : Real) /
            500000000000000000000000000000)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ((-94119513411 : Real) /
          500000000000000000000000000000) <=
          primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
            rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta ∧
        primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
            rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta <=
          ((1866608532757 : Real) /
            500000000000000000000000000000) := by
  intro eta hEta
  have hDeriv :=
    primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds
      hCombined eta hEta
  have hEq :=
    primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm
      eta
  constructor
  · rw [← hEq]
    exact hDeriv.1
  · rw [← hEq]
    exact hDeriv.2

def primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_combined_bounds
    (hCombined :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ((-94119513411 : Real) /
            500000000000000000000000000000) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <=
          ((1866608532757 : Real) /
            500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert :=
  primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_residual_bounds
    (primaryFiniteRow0Parent0Split100Sub0_fullTaylor_closedForm_residual_bounds_of_combined_bounds
      hCombined)

end Step33
end PSDpd
end Q3
