import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedLowDegreeSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Derivative-shift source for the Step33A.1-A direct collapsed degree-0 receiver.

This file keeps the actual-minus-nominal subtraction before taking norms.  It
does not try to spend an active-actual-only derivative majorant.  The remaining
source row is the signed bound for

`activeScale * D^17(ComponentProductActual) - deriv(NominalOrder16Poly)`.

The resulting first live gap is:
`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`.

It emits no numeric row and claims no Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

theorem primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_differentiableAt
    (eta : Real) :
    DifferentiableAt Real
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
      eta := by
  have hD16Diff :
      Differentiable Real
        (iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17
      |>.differentiable_iteratedDeriv 16 (by norm_num)
  have hScaledDiffAt :
      DifferentiableAt Real
        (fun t : Real =>
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
        eta :=
    hD16Diff.differentiableAt.const_mul
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
  have hNominalDiffAt :
      DifferentiableAt Real
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta := by
    unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
    exact
      rawOmegaATaylorPolynomial_differentiableAt 29 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff eta
  have hCollapsed :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression =
        fun t : Real =>
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
            primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly t := by
    funext t
    exact
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly
        t
  rw [hCollapsed]
  exact hScaledDiffAt.sub hNominalDiffAt

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_deriv_eq_activeActualD17_sub_nominalOrder16PolyDeriv
    (eta : Real) :
    deriv
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
        eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
        deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta := by
  have hD16Diff :
      Differentiable Real
        (iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17
      |>.differentiable_iteratedDeriv 16 (by norm_num)
  have hD16DiffAt :
      DifferentiableAt Real
        (iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) eta :=
    hD16Diff.differentiableAt
  have hScaledDiffAt :
      DifferentiableAt Real
        (fun t : Real =>
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
        eta :=
    hD16DiffAt.const_mul
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
  have hNominalDiffAt :
      DifferentiableAt Real
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta := by
    unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
    exact
      rawOmegaATaylorPolynomial_differentiableAt 29 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff eta
  have hScaledDeriv :
      deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
          eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          deriv
            (iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) eta :=
    deriv_const_mul
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff hD16DiffAt
  have hDerivSub :
      deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly t)
          eta =
        deriv
            (fun t : Real =>
              primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
            eta -
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta :=
    deriv_sub hScaledDiffAt hNominalDiffAt
  have hCollapsed :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression =
        fun t : Real =>
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
            primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly t := by
    funext t
    exact
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly
        t
  rw [hCollapsed, hDerivSub, hScaledDeriv]
  rw [← iteratedDeriv_succ]

/--
Degree-0 collapsed-expression receiver whose only remaining derivative source
row is a signed bound for the already-subtracted expression.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_polyDeriv_signedD17_source
    {coeff0 coeffErrorAbs derivAbs polyErrorAbs : Rat}
    (hSignedD17PolyDeriv :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
          (derivAbs : Real))
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hBudget :
      (coeffErrorAbs : Real) + (derivAbs : Real) * ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              coeff0) eta‖ <=
        (polyErrorAbs : Real) := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_deriv_bound
      ?_ ?_ hCenter hBudget
  · intro eta _hEta
    exact
      primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_differentiableAt
        eta
  · intro eta hEta
    rw [
      primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_deriv_eq_activeActualD17_sub_nominalOrder16PolyDeriv]
    exact hSignedD17PolyDeriv eta hEta

end Step33
end PSDpd
end Q3
