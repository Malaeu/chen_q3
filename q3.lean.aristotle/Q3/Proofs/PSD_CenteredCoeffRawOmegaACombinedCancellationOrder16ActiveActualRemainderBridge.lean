import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Active-actual remainder adapter for the Step33A.1-A direct scaled-remainder
target.

The direct receiver already reduces the hard row source to a remainder estimate
for `CombinedOrder16ScaledRemainderCollapsedExpression`.  The nominal
polynomial bridge identifies this collapsed expression as

`activeScale * D^16(ComponentProductActual) - nominalOrder16Poly`.

This file preserves that subtraction inside one future whole-expression row:
an approximation for the scaled active-actual derivative transports to a
collapsed-expression approximation by subtracting the exact nominal polynomial
from the same coefficient stream.  It emits no row data, interval bounds, or
Step33A.1-A closure claim.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- Candidate collapsed-expression coefficients obtained by subtracting the
exact nominal order-16 coefficient row from a future scaled-active-actual row.
This is a coefficient crosswalk only; `activeCoeff` still needs a proof-grade
analytic remainder source. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
    (activeCoeff : Fin 30 -> Rat) (j : Fin 30) : Rat :=
  activeCoeff j -
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff j

/-- The coefficient-row polynomial for `CollapsedCoeffOf activeCoeff` is the
active-actual polynomial minus the exact nominal order-16 polynomial, in the
same centered Taylor convention used by the direct Horner receiver. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedCoeffOf_poly_eq_activePoly_sub_nominal
    (activeCoeff : Fin 30 -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
          activeCoeff) eta =
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) activeCoeff eta -
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
  rw [rawOmegaATaylorPolynomial_sub_coeff]

/-- Transport a proof-grade segment approximation for the scaled
active-actual derivative into the collapsed-expression remainder row required
by the direct Horner receiver.

The premise remains the live proof-producing gap: it must come from future
proof-grade active-actual segment rows, not from sampled rows or separate
actual/nominal budget spending. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActual
    {cellL cellU polyErrorAbs : Rat} (activeCoeff : Fin 30 -> Rat)
    (hActive :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) activeCoeff eta‖ <=
          (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
              activeCoeff) eta‖ <=
        (polyErrorAbs : Real) := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly,
    primaryFiniteRow0Parent0Split100Sub0_collapsedCoeffOf_poly_eq_activePoly_sub_nominal]
  have hEq :
      (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta) -
          (rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) activeCoeff eta -
            primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta) =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) activeCoeff eta := by
    ring
  rw [hEq]
  exact hActive eta hEta

end Step33
end PSDpd
end Q3
