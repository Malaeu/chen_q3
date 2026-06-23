import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerConcretePayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Remainder bridge for the Step33A.1-A sub0 biased residual-Horner route.

The coefficient bridge identifies the residual-Horner polynomial.  This file
exposes the exact analytic remainder left by that bridge and proves how a
future proof-grade bound for that remainder fills the `residual_remainder`
field of the residual-Horner certificate.

No numerical rows are emitted here, and no Step33A.1-A closure is claimed.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- The analytic scaled remainder left after the biased residual-Horner
polynomial has been peeled off. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
      iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        eta +
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
      iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta

/-- Future proof-grade payload target for the residual-Horner remainder rows. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
    (remainderAbs : Rat) : Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
        eta‖ <=
      (remainderAbs : Real)

/-- Exact subtraction form of the already checked residual-Horner split. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_sub_hornerPoly_eq_scaledRemainder
    (eta : Real) :
    Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
        rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
          eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
        eta := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_eq_hornerPoly_add_scaledRemainder]
  unfold
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
  ring

/-- A proof-grade bound on the scaled remainder is exactly the
`residual_remainder` row needed by the residual-Horner cert on the full cell. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound
    {remainderAbs : Rat}
    (hScaled :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
        remainderAbs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
            eta‖ <=
        (remainderAbs : Real) := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_sub_hornerPoly_eq_scaledRemainder]
  exact hScaled eta hEta

/-- Segment-facing version for a future concrete residual-Horner payload. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_segmentResidualRemainder_of_scaledRemainder_bound
    {data : Step33Sub0CombinedOrder16BiasedResidualHornerCert}
    (hCell :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hPoly :
      ∀ eta : Real,
        data.poly eta =
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
            eta)
    (hScaled :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
        data.remainderAbs) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
          data.poly eta‖ <=
        (data.remainderAbs : Real) := by
  intro eta hEta
  rw [hPoly eta]
  exact
    primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound
      hScaled eta (hCell eta hEta)

end Step33
end PSDpd
end Q3
