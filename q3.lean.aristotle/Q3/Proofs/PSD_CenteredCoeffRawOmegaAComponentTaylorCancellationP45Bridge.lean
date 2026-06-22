import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Scaled P45 expression bridge for the Step33A.1-A sub0 cancellation route.

The preceding cancellation bridge identifies the component-product error with a
cancellation residual.  This file lifts that identity to the exact scaled
raw-derivative/P45 expression already consumed by the residual receiver.  It
does not prove a norm bound or a final budget comparison.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

theorem primaryFiniteRow0Parent0Split100Sub0_rawDeriv_sub_assembledPoly_eq_cancellationRhs
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta =
      (((3 : Real) / 10) / Real.pi) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta +
        ((((3 : Real) / 10) / Real.pi) -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  rw [primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_eq_scale_componentProductActual]
  rw [primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct]
  rw [primaryFiniteRow0Parent0Split100Sub0_nominalProduct_eq_componentProductNominal]
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductError_eq_cancellationResidual]
  ring

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_cancellationRhs
    (eta : Real) :
    (primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta) -
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta =
      (((3 : Real) / 10) / Real.pi) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta +
        ((((3 : Real) / 10) / Real.pi) -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  have hCross :=
    primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk
      eta
  have hEq :
      (primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
          rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta) -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta =
        primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
          rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta := by
    rw [← hCross]
    ring
  rw [hEq]
  exact
    primaryFiniteRow0Parent0Split100Sub0_rawDeriv_sub_assembledPoly_eq_cancellationRhs
      eta

end Step33
end PSDpd
end Q3
