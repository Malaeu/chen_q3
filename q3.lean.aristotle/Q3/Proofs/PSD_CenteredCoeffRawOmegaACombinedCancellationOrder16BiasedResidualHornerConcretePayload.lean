import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Concrete algebraic bridge for the Step33A.1-A sub0 biased residual-Horner
route.

This file does not emit segment rows and does not prove a valid residual-Horner
family.  It only identifies the polynomial part of the direct residual
`ComponentSource - BiasedNonzeroModelPoly` in the same Horner convention as the
checked family receiver.  The remaining proof-producing rows are the uniform
analytic remainder bounds and the exact residual-budget rows.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Coefficients of the polynomial part of the biased residual-Horner target. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
    (j : Fin 30) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff j -
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff j

/-- The residual-Horner polynomial is exactly the negative bias row. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_eq_neg_biasCoeff
    (j : Fin 30) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
        j =
      -primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelBiasCoeff
        j := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
  ring

/-- Polynomial crosswalk for the residual-Horner coefficient rows. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_nonzero_sub_biased
    (eta : Real) :
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
        eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffPoly
          eta := by
  unfold
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffPoly
  rw [← rawOmegaATaylorPolynomial_sub_coeff 29 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
    eta]

/-- The residual-Horner polynomial is the exact scalar bias correction. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_neg_bias
    (eta : Real) :
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
        eta =
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
        Real) := by
  calc
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
        eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffPoly
          eta :=
        primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_nonzero_sub_biased
          eta
    _ =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta := by
        rw [
          primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelCoeffPoly_eq]
    _ =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta +
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real)) := by
        rw [
          primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelPoly_eq]
    _ =
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
        Real) := by
        ring

/--
Exact split of the direct residual target into the residual-Horner polynomial
and the analytic remainder that must receive proof-grade segment rows.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_eq_hornerPoly_add_scaledRemainder
    (eta : Real) :
    Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta =
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
          eta +
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta +
          (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta) := by
  unfold Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_biasedNonzeroModelPoly]
  rw [
    primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_neg_bias]
  ring

end Step33
end PSDpd
end Q3
