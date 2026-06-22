import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Source-model bridge scaffolding for the Step33A.1-A sub0 combined-cancellation
high-order Taylor route.

This file deliberately does not emit generated center-jet rows, order-16 rows,
or a `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid` payload.  It
records the first structural analytic bridge that is currently local: the whole
combined expression is `C^16` once the base Step22 Omega weight is available as
`C^16`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Cauchy-style convolution for normalized center jets.  The payload generator
may use this as the exact shape for component-product jets; it is only a
definition here, not a proof that any generated row is valid. -/
def primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution
    (n : Nat) (a b : Nat -> Real) : Real :=
  (Finset.range (n + 1)).sum (fun k => a k * b (n - k))

/-- Local smoothness helper for the rational Taylor-polynomial surface used by
the combined source model. -/
theorem rawOmegaATaylorPolynomial_contDiff16
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat) :
    ContDiff Real 16 (rawOmegaATaylorPolynomial degree center coeff) := by
  unfold rawOmegaATaylorPolynomial
  fun_prop

/--
The whole combined-cancellation expression is `C^16` once the base
`step22OmegaArchWeight` source is available as `C^16`.

This closes only the structural smoothness sub-obligation of
`Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid`; it does not provide
the center-jet rows or the uniform order-16 bound.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16_of_omega
    (hOmega :
      ContDiff Real 16
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight) :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr := by
  change
    ContDiff Real 16
      (fun eta : Real =>
        rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta +
          primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta)
  simp only [
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs,
    primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly]
  have hResidualPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
  have hOmegaPrimePoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
  have hOmegaPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
  have hShapeSqPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
  have hShapeSqDerivPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff
  have hOmegaPrime :
      ContDiff Real 16 step22OmegaArchWeightDerivClosedForm :=
    step22OmegaArchWeightDerivClosedForm_contDiff16
  have hShapeSqDeriv :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10))
  fun_prop

end Step33
end PSDpd
end Q3
