import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Direct source bridge for the Step33A.1-A sub0 scaled-remainder target.

This file closes only the algebraic crosswalk requested by the direct
whole-expression row worklist: the target
`ComponentSource - NonzeroModelPoly` is the single collapsed expression

`ActiveScaleCoeff * D^16(ComponentProductActual)
 - NominalScaleCoeff * D^16(ComponentProductNominal)`.

It emits no Horner rows, no interval rows, and no Step33A.1-A closure claim.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- The collapsed direct signed expression for the nonzero-model scaled
remainder.  A future generator should approximate this whole expression as one
stream; this definition is not a bound. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
      iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
    (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
      iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta

/-- Exact collapse from the cancellation-plus-scale-mismatch split to one
whole-expression target.  This is the row-source crosswalk, not an interval
certificate. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
        eta := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly,
    primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_order16_eq_biasedResidual]
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
  ring

/-- A proof-grade full-cell interval for the collapsed expression supplies the
direct nonzero-model source proposition.  The future generator must prove the
premise; this theorem only fixes the normalization bridge. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval
    {residualAbs : Rat}
    (hInterval :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        -(residualAbs : Real) <=
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
              eta ∧
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
              eta <=
            (residualAbs : Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      residualAbs := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression,
    Real.norm_eq_abs,
    abs_le]
  exact hInterval eta hEta

/-- Canonical-budget specialization of the collapsed-expression source bridge. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_canonicalSourceProp_of_collapsed_interval
    (hInterval :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real) <=
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
              eta ∧
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
              eta <=
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
              Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval
    hInterval

end Step33
end PSDpd
end Q3
