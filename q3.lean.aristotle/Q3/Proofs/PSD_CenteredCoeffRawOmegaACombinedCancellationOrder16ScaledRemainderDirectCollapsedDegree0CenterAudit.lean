import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0CenterBudgetAudit
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0DerivativeShift

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Center audit for the Step33A.1-A direct collapsed degree-0 receiver.

This file closes only the center input for the whole collapsed expression.  It
does not provide the signed derivative row or the final degree-0 budget
comparison, so it is not a Step33A.1-A closure proof.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- Constant coefficient for the direct collapsed degree-0 row. -/
def primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0 : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0 -
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff (0 : Fin 30)

/-- Center error inherited from the active-actual center audit. -/
def primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs

theorem primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_center :
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
        ((1 : Real) / 20) =
      (primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff
        (0 : Fin 30) : Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
  simpa using
    rawOmegaATaylorPolynomial_center 29 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff

theorem
    primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated :
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          ((1 : Real) / 20) -
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0 :
          Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
        Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly]
  rw [primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_center]
  have hEq :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                ((1 : Real) / 20) -
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff
            (0 : Fin 30) : Real) -
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0 :
          Real) =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
              ((1 : Real) / 20) -
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0 :
          Real) := by
    unfold primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0
    norm_num [Rat.cast_sub]
  rw [hEq]
  simpa [
    primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs]
    using
      primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_hCenter_generated

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_center_and_polyDeriv_source
    {derivAbs polyErrorAbs : Rat}
    (hSignedD17PolyDeriv :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
          (derivAbs : Real))
    (hBudget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (polyErrorAbs : Real) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_polyDeriv_signedD17_source
      hSignedD17PolyDeriv
      primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated
      hBudget

end Step33
end PSDpd
end Q3
